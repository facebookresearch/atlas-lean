# Main Data Copy Decr Traced?

State-level wrapper around the shared-store decrementing copy.  Cursor
arithmetic is signed, so copying cell zero legitimately returns `-1`.
