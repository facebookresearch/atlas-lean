# Coupled

Couple one program to storage. A `none` transition is local to the program. A `some` read,
write, fence, acquire or release must be taken by both systems with exactly the same label.
A `some (.flush p)` transition is taken by storage alone, keeping the program state fixed;
any flush-labelled entries in the program relation are ignored.
