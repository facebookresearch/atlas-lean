# Result of inserting into a B-tree subtree

An insertion result over a key type $\alpha$
is either a single tree over $\alpha$, or a triple $(\ell, m, r)$ of two trees $\ell$ and $r$
over $\alpha$ and a key $m$ of $\alpha$. In insertion, the first form is a subtree that did not
split, and the second form is an overflowing node split into two trees of the same height, with
the median key $m$ promoted between them; the type itself does not record heights.
