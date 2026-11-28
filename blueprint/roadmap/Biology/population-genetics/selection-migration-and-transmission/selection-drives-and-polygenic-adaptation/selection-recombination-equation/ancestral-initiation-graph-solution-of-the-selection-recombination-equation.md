# Ancestral initiation graph solution of the selection–recombination equation

**Model.** Take sites $S=\{1,\dots,n\}$ with two alleles per site, type space $X=\{0,1\}^n$, and let $\omega_t\in\mathcal P(X)$ be the type distribution of an infinite haploid population. One site $i_\bullet$ is under selection: types with $x_{i_\bullet}=0$ reproduce at rate $1+s$ ($s>0$) and the others at rate $1$. Single crossovers at sites $i\in S^\circ=S\setminus\{i_\bullet\}$ occur at rates $\varrho_i\ge0$. A crossover at $i$ splits a sequence into the *tail* $D_i$ (the sites on the far side of $i$ from $i_\bullet$, including $i$) and the *head* $C_i=S\setminus D_i\ni i_\bullet$. The selection–recombination equation is

$$\dot\omega_t=s\bigl(F(\omega_t)-f(\omega_t)\,\omega_t\bigr)+\sum_{i\in S^\circ}\varrho_i\bigl(\omega_{t,C_i}\otimes\omega_{t,D_i}-\omega_t\bigr),$$

where $f(\nu)=\nu_{i_\bullet}(0)$ is the fit proportion, $F(\nu)(x)=(1-x_{i_\bullet})\nu(x)$, and $\nu_U$ is the marginal on $U$. The pure selection flow is explicit:

$$\varphi_t(\nu)=\frac{e^{st}F(\nu)+(\mathrm{id}-F)(\nu)}{e^{st}f(\nu)+1-f(\nu)}.$$

**Ancestral initiation graph (AIG).** Grow a random graph of length $t$ backwards in time from a root, the sampled individual. Each line is hit by $i$-splittings at rate $\varrho_i$, independently over $i\in S^\circ$. At a splitting the upper line, which carries the head $C_i$, continues, and a new lower line, which carries the tail $D_i$, starts with age $0$. Every leaf is labelled by the *selective age* $\theta$ of its line, meaning the time since that line split off (or $t$ for the original line). Given an initial distribution $\nu$, each leaf of age $\theta$ gets a type drawn from $\varphi_\theta(\nu)$. Types are then propagated toward the root: at an $i$-splitting the descendant takes the $C_i$ alleles of the upper line and the $D_i$ alleles of the lower line. Let $\Gamma_t(\nu)$ be the law of the type delivered at the root.

**Theorem.** The solution of the selection–recombination equation with initial value $\omega_0$ is the mean delivered law:

$$\omega_t=\mathbb E\bigl[\Gamma_t(\omega_0)\bigr].$$

Equivalently, order the sites outward from $i_\bullet$ as $i_0=i_\bullet,i_1,\dots,i_{n-1}$, and let $\omega^{(k)}$ solve the equation with only the first $k$ crossover sites active. Then

$$\omega^{(k)}_t=e^{-\varrho^{(k)}t}\,\omega^{(k-1)}_t+\omega^{(k-1)}_{C^{(k)},t}\otimes\int_0^t\varrho^{(k)}e^{-\varrho^{(k)}\tau}\,\omega^{(k-1)}_{D^{(k)},\tau}\,d\tau,\qquad 0<k<n,$$

with $\omega^{(0)}_t=\varphi_t(\omega_0)$.

## Expansion

Discretize with the Euler step $T_h(\nu)=\nu+h\Psi(\nu)$. The selection step $\nu\mapsto\nu+h\Psi_{\rm sel}(\nu)$ is linear on each level set of $f$, and a recombinator does not change $f$. So one Euler step equals sampling: with probability $1-h\sum_i\varrho_i$ apply selection, and with probability $h\varrho_i$ replace the tail by a fresh sample whose selective clock restarts at zero. This gives a discrete $h$-AIG whose delivered type has law $\widetilde T_h^k(\nu)$, by induction on $k$. As $h\to0$ the geometric waiting times between splittings become exponential and the Euler scheme converges, which yields the continuous AIG. Conditioning on the first splitting at the outermost active site produces the recursion: with probability $e^{-\varrho^{(k)}t}$ no split occurs, and otherwise the tail is an independent sample from the population at an exponential time.

## Sources

- Frederic Alberti, Carolin Herrmann, Ellen Baake, "Selection, recombination, and the ancestral initiation graph", *Theoretical Population Biology* 142 (2021), 46–56, <https://doi.org/10.1016/j.tpb.2021.08.001>; preprint arXiv:2101.10080 (2021), Section 2 (selection–recombination equation and Theorem 2.2), Section 3 (Definition 3.3, Proposition 3.5, Definition 3.6 and the representation of the solution as the mean delivered law), <https://doi.org/10.48550/arXiv.2101.10080>.
