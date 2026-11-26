# Bottom-up handle splay

Starting at a live handle, rotate within its auxiliary tree,
first rotating the parent in a zig-zig and the target in a zig-zag. A last unpaired edge gives
a zig at the top. Charge one unit per rotation and one for completion.
