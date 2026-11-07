# Needleman–Wunsch score

Given a type $\alpha$, a substitution score
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$, the
Needleman–Wunsch score $\mathrm{NW}(xs, ys)$ of two lists over $\alpha$ is defined by recursion
on their total length: if one of the lists is empty, it is $g$ times the length of the other;
and for lists $a\,xs$ and $b\,ys$ with heads $a$, $b$ and tails $xs$, $ys$,

$$\mathrm{NW}(a\,xs, b\,ys) = \max\bigl(\mathrm{NW}(xs, ys) + \sigma(a, b),
\ \mathrm{NW}(xs, b\,ys) + g,\ \mathrm{NW}(a\,xs, ys) + g\bigr).$$

By the Needleman–Wunsch optimality theorem, this is the optimal global alignment score of the
two lists.
