# A minimum active role owned by a guard is its subject key

Let $\Delta$ be an ownership context, $e$, $d$ endpoints and $c$, $u$ capabilities with $\Delta(e) =
c$ and $\Delta(d) = u$, both active (protocols heads other than $\mathrm{end}$). Suppose
$\mathrm{Min}_\Delta(d,k)$ holds for $k$ the rank of $u$ (every endpoint other than $d$ with an
active capability has rank $> k$), and the rank of $c$ is at most the rank of every active
capability of $\Delta$. Then $e = d$.
