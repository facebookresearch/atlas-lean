# The base-case alignment is optimal

Fix a type $\alpha$, a substitution score
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$. For all lists
$xs$, $ys$ over $\alpha$ with $|xs| \le 1$ and $|ys| \le 1$, the alignment score of the
base-case alignment of $xs$ and $ys$ equals the Needleman–Wunsch score of $xs$ and $ys$.
