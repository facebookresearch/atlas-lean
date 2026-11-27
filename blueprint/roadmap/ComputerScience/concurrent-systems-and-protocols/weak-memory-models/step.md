# x86-TSO storage transitions

A transition relates a storage state, an event, and a resulting storage state. A thread is
unblocked when the lock is free or the thread owns it. Exactly these transitions are allowed:

- An unblocked thread reads the shared value at an address if its local buffer has no write to
  that address, or reads the newest local buffered value for that address otherwise. Neither read
  changes the state.
- Any thread can enqueue an address-value pair at the newest end of its local buffer. Only that
  buffer changes.
- An unblocked thread with a nonempty local buffer can flush its oldest write, removing that
  entry and replacing the value at its address in shared memory. All other components stay fixed.
- A thread with an empty local buffer can execute MFENCE. Neither the lock nor any other part
  of the state changes, and the thread need not be unblocked.
- A thread can acquire a free lock if its local buffer is empty; it becomes the owner. A thread
  can release the lock if it owns the lock and its local buffer is empty; the lock becomes free.
  Both steps leave memory and all buffers unchanged.
