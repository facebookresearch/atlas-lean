# Packed memory arrays

A *packed memory array* stores $N$ ordered elements in an array of $\Theta(N)$ slots, in sorted order with gaps. The array is divided into segments of $\Theta(\log N)$ slots, and an implicit complete binary tree over the segments assigns to each node (a contiguous window of slots) an upper density threshold that decreases linearly from close to $1$ at the leaves to a constant below $1$ at the root, and a lower threshold increasing correspondingly. To insert, place the element in its segment; if the segment exceeds its threshold, find the nearest ancestor window within its thresholds and redistribute its elements evenly.

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
