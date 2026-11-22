# Number of rotations performed by splaying

Over a linear order, the number of rotations performed by the [splay operation](splay.md) at a key
$x$ on a binary tree is defined recursively. It is $0$ for the empty tree. For a node with key $k$,
left subtree $l$ and right subtree $r$:

- if $x = k$, it is $0$;
- if $x < k$: it is $0$ if $l$ is empty; otherwise, with $l$ having key $k'$ and subtrees $l'$
  (left) and $r'$ (right), it is $1$ if $x = k'$; if $x < k'$ it is $1$ when $l'$ is empty and
  two plus the number of rotations for $x$ on $l'$ otherwise; if $x > k'$ it is $1$ when $r'$ is
  empty and two plus the number of rotations for $x$ on $r'$ otherwise;
- if $x > k$: symmetrically, it is $0$ if $r$ is empty; otherwise, with $r$ having key $k'$ and
  subtrees $l'$ and $r'$, it is $1$ if $x = k'$; if $x > k'$ it is $1$ when $r'$ is empty and two
  plus the number of rotations for $x$ on $r'$ otherwise; if $x < k'$ it is $1$ when $l'$ is empty
  and two plus the number of rotations for $x$ on $l'$ otherwise.

A zig step counts one rotation and a zig-zig or zig-zag step counts two.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2 (zig, zig-zig and zig-zag steps).
