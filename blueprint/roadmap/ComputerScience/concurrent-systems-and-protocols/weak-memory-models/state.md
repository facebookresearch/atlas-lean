# x86-TSO storage state

The x86-TSO storage state consists of a total shared-memory map from addresses to values,
one buffer of pending address-value pairs per thread, and an optional global lock owner.
Each buffer lists its writes from oldest to newest. No lock owner means the lock is free.
