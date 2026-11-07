# Every cut of the second list extends to an optimal split

Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $S(u, v)$ for the Needleman–Wunsch score of lists $u$, $v$, and $u_{\lt m}$ for the first
$m$ elements of $u$ and $u_{\ge m}$ for the rest. For all lists $xs$, $ys$ over $\alpha$ and
every $m \le |ys|$, there is $k \le |xs|$ with
$S(xs_{\lt k}, ys_{\lt m}) + S(xs_{\ge k}, ys_{\ge m}) = S(xs, ys)$.
