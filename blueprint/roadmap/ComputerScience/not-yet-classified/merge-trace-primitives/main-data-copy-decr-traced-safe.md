# Main Data Copy Decr Traced safe

A single main-to-main decrementing copy needs only bounds for the two
dereferences.  No cursor-positivity premise is imposed: after copying index
zero the exact signed post-cursor is the legal sentinel `-1`.
