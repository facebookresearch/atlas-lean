# Reachability for neural-network control systems is undecidable

No algorithm decides whether a discrete-time control loop with a ReLU neural network controller reaches a target polyhedron from an initial polyhedron. Undecidability holds already for integer weights, a single hidden layer, a single initial state and a target fixing one output coordinate.

**Theorem (Schilling and Zimmermann).** The [reachability problem for neural-network control systems](neural-network-control-systems.md) is undecidable: given a DNN $N$ with rational weights and identity or ReLU activations, a plant $f$, and polyhedra $X_0$ and $T$, it cannot be decided whether $\Phi^k(\vec{x}_0) \in T$ for some $\vec{x}_0 \in X_0$ and $k \in \mathbb{N}$.

The paper sharpens this in two corollaries, both with the plant $f(\vec{x}, \vec{u}) = \vec{u}$: the problem stays undecidable for DNNs with integer weights, input and output dimension $3$, six hidden layers, a singleton initial set and a target of the form $o = v$ for one output neuron $o$ and a constant $v \in \mathbb{N}$ (Corollary 1); and for DNNs with integer weights and one hidden layer, again with a singleton initial set and a target $o = v$ (Corollary 2). The paper also shows that the problem is semi-decidable for plants definable in the same Büchi-automaton encoding of real functions that captures ReLU networks.

## Depends on

- [Neural-network control systems](neural-network-control-systems.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from halting of two-counter machines with instructions increment, decrement (truncated at $0$) and jump-if-zero. The state $(\ell, c_0, c_1) \in \mathbb{R}^3$ holds the program counter and the counters; the plant returns the control input, and the DNN, whose hidden neurons use ReLU and whose output neurons use the identity, has one gadget per instruction that performs that instruction when the program-counter input equals its line number and computes the identity otherwise. Starting from $X_0 = \{(0,0,0)\}$, the machine halts exactly when a state with $\ell = k - 1$, the line of the halting instruction, is reached. For one hidden layer, the six hidden layers are stacked side by side as tracks of one wide layer, so that seven iterations of the new network simulate one iteration of the old, and a modulo-$7$ counter gadget restricts the target to every seventh step.

## Sources

- Christian Schilling and Martin Zimmermann, "The Reachability Problem for Neural-Network Control Systems", Bridging the Gap Between AI and Reality (AISoLA 2023), Lecture Notes in Computer Science, pp. 455–469, Springer, 2024, <https://doi.org/10.1007/978-3-031-73741-1_27>; Theorem 1 with its proof, Corollaries 1 and 2 in Section 3, and Section 4 (semi-decidability) of arXiv:2407.04988v2 (the copy read), <https://arxiv.org/abs/2407.04988v2>.
