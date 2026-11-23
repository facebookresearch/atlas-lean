# Strong Markov property for everywhere-finite stopping times

Let $S$ be a nonempty
standard Borel space, $\mu$ a finite measure on $S$, $\kappa$ a Markov kernel on $S$, and $P_\mu$
the law on the path space $S^{\mathbb{N}}$ of the Markov chain with initial distribution $\mu$ and
transition kernel $\kappa$; for $x \in S$ write $E_x$ for the expectation under the chain started
from $x$. Let $T : S^{\mathbb{N}} \to \mathbb{N}$ be a stopping time for the path filtration, with
$\sigma$-algebra $\mathcal{F}_T$, and let $Y_n : S^{\mathbb{N}} \to \mathbb{R}$, for
$n \in \mathbb{N}$, be measurable functions with $|Y_n(\omega)| \le C$ for a single constant $C$
and all $n$ and $\omega$. Write $\theta_T \omega$ for the path $\omega$ shifted by $T$, namely
$k \mapsto \omega(T(\omega) + k)$. Then the conditional expectation under $P_\mu$ given
$\mathcal{F}_T$ of $\omega \mapsto Y_{T(\omega)}(\theta_T \omega)$ equals
$\omega \mapsto E_{\omega(T(\omega))}[Y_{T(\omega)}]$ $P_\mu$-almost surely.

This is the special case of the strong Markov property for a.s.-finite stopping times in which
the time is finite everywhere.
