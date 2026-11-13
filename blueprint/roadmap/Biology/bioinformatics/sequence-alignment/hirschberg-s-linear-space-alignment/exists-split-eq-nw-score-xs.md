# Every cut of the first list extends to an optimal split

Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $S(u, v)$ for the Needleman–Wunsch score of lists $u$, $v$, and $u_{\lt m}$ for the first
$m$ elements of $u$ and $u_{\ge m}$ for the rest. For all lists $xs$, $ys$ over $\alpha$ and
every $m \le |xs|$, there is $k \le |ys|$ with
$S(xs_{\lt m}, ys_{\lt k}) + S(xs_{\ge m}, ys_{\ge k}) = S(xs, ys)$.
