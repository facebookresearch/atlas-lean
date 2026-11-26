# Termination-insensitive noninterference for programs with output

Model a deterministic program $C$ by a labelled transition system on configurations $\langle C, M\rangle$, where a memory $M = LH$ is a pair of a low (public) part $L$
and a high (secret) part $H$, and a step $\langle C, M\rangle \xrightarrow{\ell} \langle C', M'\rangle$ produces a low observable output $\ell$; $\langle C, M\rangle\Uparrow$ means that no
further output follows. Let $\vec\alpha$ range over output sequences $\vec\ell$ and $\vec\ell\Uparrow$. For a low input $L$, the *observations* are
$\mathrm{Obs}(C, L) = \{\vec\alpha \mid \langle C, LH\rangle \xrightarrow{\vec\alpha} \text{ for some } H\}$, and the attacker's *knowledge* after observing $\vec\alpha$ is
$k(C, L, \vec\alpha) = \{H \mid \langle C, LH\rangle \xrightarrow{\vec\alpha}\}$, the set of secrets consistent with the observation.

$C$ satisfies *termination-insensitive noninterference* (TINI) if whenever $\vec\ell\ell \in \mathrm{Obs}(C, L)$ with $\ell$ an output,

$$k(C, L, \vec\ell\ell) = \bigcup_{\ell'} k(C, L, \vec\ell\ell'),$$

the union over outputs $\ell'$: the value of each output teaches nothing beyond the fact that some output occurs, while observing divergence is unrestricted.
It generalizes the batch-job condition of [Volpano–Smith–Irvine noninterference](noninterference-for-the-volpanosmithirvine-type.md), which ignores
nonterminating runs and intermediate outputs, and is weaker than requiring $k(C, L, \vec\ell\alpha) = k(C, L, \vec\ell)$ for every observation, the
termination-sensitive condition.

## Sources

- A. Askarov, S. Hunt, A. Sabelfeld and D. Sands, "Termination-insensitive noninterference leaks more than just a bit", *Computer Security – ESORICS 2008*, Springer, 2008, copy at <https://www.cse.chalmers.se/~andrei/esorics08.pdf>: Section 2, Definitions 2–5.
