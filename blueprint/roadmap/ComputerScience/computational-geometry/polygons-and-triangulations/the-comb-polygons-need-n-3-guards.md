# The comb polygons need ⌊n/3⌋ guards

For every $k \ge 1$ there is a simple polygon with $n = 3k$ vertices, the *comb* with $k$ prongs, such that no set of fewer than $k$ points of the polygon sees every point of it, where a point $g$ sees $p$ if the segment $gp$ lies in the polygon. No point sees the tips of two different prongs, so each prong needs its own guard. Together with [Chvátal's art gallery theorem](chvatal-s-art-gallery-theorem.md) this shows that $\lfloor n/3 \rfloor$ guards are sometimes necessary and always sufficient.

## Depends on

- [Chvátal's art gallery theorem](chvatal-s-art-gallery-theorem.md)

## Proof depends on

- [Chvátal's art gallery theorem](chvatal-s-art-gallery-theorem.md)

## Sources

- J. O'Rourke, *Art Gallery Theorems and Algorithms*, Oxford University Press, 1987, Chapter 1, <https://www.science.smith.edu/~jorourke/books/ArtGalleryTheorems/Art_Gallery_Chapter_1.pdf>: Section 1.2.1, pp. 2–3, and Fig. 1.2, the comb of $k$ prongs and $n = 3k$ edges that requires $k$ guards (Chvátal 1975), establishing $g(n) \ge \lfloor n/3 \rfloor$
