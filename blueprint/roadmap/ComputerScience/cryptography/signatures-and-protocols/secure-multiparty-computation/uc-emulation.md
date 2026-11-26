# UC emulation

In Canetti's static-system presentation (UC4SS), the set of machines is fixed, not their order of activation. Fix two compatible protocols $\pi$ and $\phi$ with the same external interface. The environment $E$ (identity 0) calls the main parties and the intermediary $A$ (identity 1). The intermediary and the protocol machines communicate on backdoor ports. An external identity of the protocol is an identity absent from it that has a subroutine in it; in the execution these external caller identities translate to 0.

An execution starts with $E$ active on input $z$. The active machine can write a message to a permitted destination identity and port. The recipient then becomes active and learns both the message and the sender's identity (translated when applicable). Only $E$ may choose the apparent source identity that its recipient learns. If a non-environment machine yields without sending, control returns to $E$; if $E$ yields without sending, the execution ends. Assume the compared experiments terminate and hence have probability laws. The observable is **the bit in the environment's output register**, not a transcript. Write $X_{\pi,E,A}(k,z)$ for its law over the random choices of all machines, on security parameter $k$ and auxiliary bit string $z$, and $p_{\pi,E,A}(k,z)$ for its probability of true.

For the uniform-code convention, $k$ is supplied in unary and a machine is one probabilistic program across all $k$, not a new advice string or circuit chosen at each $k$. Its time bound counts its own steps across **all** activations and coin outcomes. It is polynomial if some fixed power of $k$ bounds that time for all sufficiently large $k$. Allow $z$ to be any finite bit string on a read-only input tape of $E$: the clock is in $k$, not in $k+|z|$, and reading the whole string is not a unit operation. The tutorial describes polynomially bounded families; uniform code and this input-access convention specify which version is meant here.

**Qualitative emulation.** For every fixed polynomial-time $A$ there exists a fixed polynomial-time simulator $S$ such that, for every fixed polynomial-time $E$ and every positive integer $c$, there is a threshold $K\ge 1$ with

$$
\forall k\ge K\;\forall z\in\{0,1\}^*,\qquad |p_{\pi,E,A}(k,z)-p_{\phi,E,S}(k,z)|\le k^{-c}.
$$

The simulator can depend on $A$ but not on $E$, $k$ or $z$. The threshold can depend on the programs and $c$, not on $z$. Equivalently, for each such $E$, the supremum of the bit advantage over $z$ is a single negligible function of $k$.

**Quantitative emulation.** Fix a time-overhead function $\delta:\mathbb N\to\mathbb N$ and slack $\varepsilon:\mathbb N\to\mathbb R$. For every $A$ with clock bound $t_A(k)$ there is an $S$ whose time at each $k$ is at most $\delta(t_A(k))$. For every $E$, parameter $k$, time bound $t_E$ for $E$ at that parameter, and input $z$,

$$
d_{\rm TV}\bigl(X_{\pi,E,A}(k,z),X_{\phi,E,S}(k,z)\bigr)<\varepsilon(t_E).
$$

For a multiplicative slowdown $d$ take $\delta(t)=dt$. The comparison is strict, including at zero slack. On two bit laws $P,Q$, total variation is $|P(1)-Q(1)|$; there is no assertion that the laws of the entire views have that distance.

**Ideal protocols and the dummy.** A protocol realizes a functionality $\mathcal F$ if it emulates $I_{\mathcal F}$: its visible party identities forward API inputs and outputs to and from the trusted central machine, whose backdoor connects to the simulator. These party relays are not the dummy *adversary* $D$. The latter forwards an addressed command $(i,m)$ from $E$ to party $i$ and returns the source-tagged reply $(i,m')$.

In UC4SS the qualitative reduction runs $A$ inside a new environment $E_A$ and composes $A$ with a simulator $S_D$ for $D$ to obtain $S_A$. It needs closed, efficiently interpretable machines for both constructions: relaying must preserve identifiers, ports, private coins, activation order and the final bit, with polynomial running time. Then the real experiments with $(E,A)$ and $(E_A,D)$ have equal laws, as do the ideal experiments with $(E_A,S_D)$ and $(E,S_A)$. The dummy comparison for $E_A$ therefore gives the desired comparison for $E$. This does not give unchanged quantitative bounds for the wrappers. The fixed machine set of UC4SS does not cover dynamically created machines in general UC.

The [one-exchange execution law](exec.md), [qualitative comparison](emulates.md), [strict quantitative comparison](emulates-within.md) and [dummy reduction](emulates-iff-dummy.md) specialize these ideas to one main party, a prescribed order of one-bit messages and uniform finite-register programs. The environment, intermediary and party are three wired roles, not three external caller identities of the protocol. They do not characterize all polynomial-time UC machines.

## Depends on

- [Efficient adversaries: one uniform probabilistic program on a unary security parameter](../../security-games/asymptotic-security/efficient-adversaries.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)
- [Bit advantage equals statistical distance](../../security-games/games-and-advantages/advantage-eq-dist.md)

## Sources

- R. Canetti, [*Universally Composable Security: A Tutorial*](https://www.bu.edu/riscs/files/2025/08/Canetti.pdf), UC/EasyUC Summer School, Boston University (2025), slides 14–22 (static systems, execution and resource bounds), 23–24 (qualitative and quantitative emulation), 25–27 (ideal protocol and realization), 50–53 (dummy and simulator construction).
