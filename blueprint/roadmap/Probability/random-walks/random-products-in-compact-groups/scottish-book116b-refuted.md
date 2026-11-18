# Scottish Book Problem 116(b) fails for arbitrary measurable sets

The measurable-set form
of Scottish Book Problem 116(b) is false. For $\varphi, \psi$ in a group $G$ and a Boolean
sequence $c : \mathbb{N} \to \{\mathrm{false}, \mathrm{true}\}$, let $f_{n+1} = \varphi$ if
$c(n) = \mathrm{false}$ and $f_{n+1} = \psi$ if $c(n) = \mathrm{true}$, and define the successive
products by $P_0 = 1$ and $P_{n+1} = P_n f_{n+1}$. It is not the case that for every compact
Hausdorff topological group $G$ with its Borel $\sigma$-algebra and Haar probability measure
$\mu$, for $(\mu \otimes \mu)$-almost every pair $(\varphi, \psi) \in G \times G$ generating a
dense subgroup of $G$, for almost every $c$ under the fair coin product measure and every
measurable set $V \subseteq G$, the proportion of $P_0, \ldots, P_{N-1}$ that lie in $V$ tends
to $\mu(V)$ as $N \to \infty$.

Counterexample: take $G$ to be the circle $S^1$ with normalized Lebesgue measure. Almost every
pair $(\varphi, \psi)$ generates a dense subgroup. For any such pair and any $c$, the set $V_c$
of all successive products is countable, hence measurable with $\mu(V_c) = 0$, yet every
successive product lies in $V_c$, so the proportion equals $1$ for every $N \ge 1$. The set $V$
may depend on $c$ because it is quantified after $c$, and the only condition on $V$ is
measurability. The version restricted to sets $V$ whose frontier has measure $0$ is a different
statement, filed separately in OpenConjectures.

## Sources

- J. Schreier and S. Ulam, Problem 116, part (b) of the Scottish Book, typescript PDF p. 56, printed p. 53; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
