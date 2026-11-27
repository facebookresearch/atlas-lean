# Congested clique lower bounds imply circuit lower bounds

Consider the congested clique with $n$ processors and $b'$-bit messages, computing a Boolean function $f : \{0,1\}^{n^2} \to \{0,1\}$. A function $g : \{0,1\}^m \to \{0,1\}$ is $b$-separable if for every partition of its inputs into blocks $I_1, \dots, I_k$ there are functions $g_j$ with $b$-bit outputs and $h$ with $g(x) = h(g_1(x_{I_1}), \dots, g_k(x_{I_k}))$. Suppose $f$ is computed by a circuit of depth $D$ with $n^2 s$ wires whose gates have unbounded fan-in and fan-out and are $b$-separable. Then, for every input partition that gives each processor at most $n(b + s)$ input wires, $f$ can be computed in $O(D)$ rounds with messages of $O(b + s)$ bits. AND, OR, NOT and $\mathrm{MOD}_m$ gates for constant $m$ are $O(1)$-separable, and unweighted threshold gates are $O(\log n)$-separable. Consequently there are constants $\alpha, \beta > 0$ such that a lower bound of $\alpha \log\log n$ rounds for an explicit function with $\beta \log n$-bit messages would improve the best known wire lower bounds for constant-depth unweighted threshold circuits, and a sufficiently slowly growing super-constant round lower bound for an explicit function with $\beta$-bit messages would improve the best known wire lower bounds for constant-depth circuits of $\mathrm{MOD}_m$ gates with composite $m$. The simulation covers only circuits obeying these separability, wire and input-balance bounds, not arbitrary polynomial-size circuits. In contrast, when each processor holds $n$ input bits, a counting argument shows that some Boolean function of the $n^2$ input bits requires $(n - O(\log n))/b'$ rounds, which is $\Omega(n/\log n)$ for $b' = \Theta(\log n)$.

## Proof sketch

Assign gates to processors so that each processor owns at most one heavy gate (one with at least $ns$ incident wires; there are at most $n$ of them) and light gates of total weight at most $2ns$, and evaluate the circuit layer by layer. For a heavy gate, each processor owning some of its inputs applies the corresponding function $g_j$ and sends the $b$-bit value to the gate's owner, which applies $h$; the values of light gates are routed by Lenzen routing, since each processor sends and receives at most $2ns$ bits for light-gate wires. Each layer then costs $O(1)$ rounds with $O(b + s)$-bit messages, and the initial input distribution is routed the same way. For the counting bound, a $t$-round protocol is determined by the processors' local functions on their inputs and at most $t n b'$ received bits, which bounds the number of computable functions below $2^{2^{n^2}}$ unless $t \ge (n - O(\log n))/b'$.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- A. Drucker, F. Kuhn, R. Oshman, "On the Power of the Congested Clique Model", PODC 2014, Definition 1, Theorems 2 and 4, and Section 2.
