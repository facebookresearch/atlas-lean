# Sorted rotations of a sentinel-terminated text

Let $t = t_0 \cdots t_{n-1}$ be a text over a linearly ordered alphabet and $u = t\bot$ the text
followed by a sentinel $\bot$ smaller than every letter. The sorted rotations of $t$ form the list
$R$ of the positions $0, \dots, n$ sorted (stably, starting from increasing order) by their
rotations $u_i \cdots u_n u_0 \cdots u_{i-1}$ in lexicographic order. Row $r$ of the
Burrows–Wheeler matrix is the rotation of $u$ starting at $R[r]$.
