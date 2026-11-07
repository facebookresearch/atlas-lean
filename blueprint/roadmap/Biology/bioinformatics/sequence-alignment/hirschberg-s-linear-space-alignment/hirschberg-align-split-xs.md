# Hirschberg reconstruction splits the longer first list

Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $H_n(u, v)$ for the Hirschberg reconstruction of lists $u$, $v$ with fuel $n$, $S(u, v)$
for their Needleman–Wunsch score, and $u_{\lt m}$, $u_{\ge m}$ for the first $m$ elements of $u$
and the rest. Let $xs$, $ys$ be lists over $\alpha$ that are not both of length at most $1$,
with $|ys| < |xs|$. Put $h = \lfloor |xs| / 2 \rfloor$ and let $k$ be the least maximizer over
$\{0, \dots, |ys|\}$ of $j \mapsto S(xs_{\lt h}, ys_{\lt j}) + S(xs_{\ge h}, ys_{\ge j})$. Then
for every $n \in \mathbb{N}$, $H_{n+1}(xs, ys)$ is the concatenation of
$H_n(xs_{\lt h}, ys_{\lt k})$ and $H_n(xs_{\ge h}, ys_{\ge k})$.
