# Strong Markov property for a.s.-finite stopping times

Let $S$ be a nonempty standard
Borel space, $\mu$ a finite measure on $S$, $\kappa$ a Markov kernel on $S$, and $P_\mu$ the law
on the path space $S^{\mathbb{N}}$ of the Markov chain with initial distribution $\mu$ and
transition kernel $\kappa$. For $x \in S$ write $E_x$ for the expectation under the chain started
from $x$, and for a path $\omega$ and $n \in \mathbb{N}$ write $\theta_n \omega$ for the shifted
path $k \mapsto \omega(n + k)$. Let $T : S^{\mathbb{N}} \to \mathbb{N} \cup \{\infty\}$ be a
stopping time for the path filtration, with $\sigma$-algebra $\mathcal{F}_T$, such that
$T \ne \infty$ $P_\mu$-almost surely, and let $Y_n : S^{\mathbb{N}} \to \mathbb{R}$, for
$n \in \mathbb{N}$, be measurable functions with $|Y_n(\omega)| \le C$ for a single constant $C$
and all $n$ and $\omega$. Then the conditional expectation under $P_\mu$ given $\mathcal{F}_T$ of
$\omega \mapsto Y_{T(\omega)}(\theta_{T(\omega)} \omega)$ equals
$\omega \mapsto E_{\omega(T(\omega))}[Y_{T(\omega)}]$ $P_\mu$-almost surely.

On the null event $\{T = \infty\}$ both sides are evaluated at the same unspecified finite time,
which does not affect the almost-sure equality.

## Sources

- Theory of Probability, Lecture 31 (strong Markov property).
