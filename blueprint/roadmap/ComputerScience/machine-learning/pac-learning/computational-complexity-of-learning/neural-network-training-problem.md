# The neural network training problem

The training problem asks whether the weights and biases of a feedforward network with a given architecture and activation functions can be chosen so that the total cost on finitely many rational data points meets a threshold. The class of allowed activation functions is a parameter.

**Architectures (Hankala, Hannula, Kontinen and Virtema).** A *neural network architecture* is a pair $\mathcal{N} = (G, \phi)$ of a finite directed acyclic graph $G = (V, E)$ and a map $\phi$ assigning to each non-input neuron $v$ an activation function $\phi_v : \mathbb{R} \to \mathbb{R}$. Input neurons have no incoming edges, output neurons no outgoing edges, and the others are hidden. A *neural network* $(\mathcal{N}, w, b)$ adds real edge weights $w(e)$ and real biases $b_v$ for the non-input neurons. A *data point* $d$ maps every input and output neuron to a real number. The *neural function* $g$ assigns to each data point $d$ the neural values $g_d(v) = d(v)$ for input neurons and

$$
g_d(v) = \phi_v\Bigl(b_v + \sum_{u \in P(v)} w(u, v)\, g_d(u)\Bigr)
$$

for the other neurons, where $P(v)$ is the set of predecessors of $v$; write $(g_d)_O$ and $d_O$ for the tuples of values at the $m$ output neurons in a fixed order.

**The problem.** Let $\tau$ be a set of unary real functions. An $\mathrm{NN}_\tau$-TRAINING instance is a tuple $(\mathcal{N}, A_E, A_V, D, c, \prec, \delta)$ with an architecture $\mathcal{N}$ in which every activation function is the identity or a member of $\tau$; a set $A_E$ of active edges and a set $A_V$ of active neurons; a finite set $D$ of data points with rational values; a cost function $c : \mathbb{R}^{2m} \to \mathbb{R}$ definable by an arithmetic expression; a relation symbol $\prec \in \{=, \le, <\}$; and a rational threshold $\delta$. A pair $(w, b)$ is a *satisfying solution* if $w(e) = 1$ for every edge $e \notin A_E$, $b_v = 0$ for every neuron $v \notin A_V$, and

$$
\sum_{d \in D} c\bigl((g_d)_O, d_O\bigr) \prec \delta.
$$

$\mathrm{NN}_\tau$-TRAINING asks whether a satisfying solution exists; $\mathrm{NN}_f$-TRAINING abbreviates $\mathrm{NN}_{\{f\}}$-TRAINING, and the variant $\mathrm{NN}_\tau$-TRAINING$^<$ allows only $\prec$ equal to $<$.

## Depends on

None.

## Proof depends on

None.

## Expansion

For linear (identity) activations the problem is the training problem known to be complete for the existential theory of the reals; with a faithful non-negative cost, threshold $0$ and equality, a satisfying solution is a network fitting every data point exactly. The source shows that for every $\tau$ the problem is complete for the class of problems reducible in polynomial time to existential sentences over the reals with the functions of $\tau$ (its Theorem 23).

## Sources

- Teemu Hankala, Miika Hannula, Juha Kontinen and Jonni Virtema, "Complexity of Neural Network Training and ETR: Extensions with Effectively Continuous Functions", Proceedings of the AAAI Conference on Artificial Intelligence 38(11), pp. 12278–12285, 2024, <https://doi.org/10.1609/aaai.v38i11.29118>. Read in arXiv:2305.11833v1, <https://arxiv.org/abs/2305.11833v1>; Definitions 14–18 and Theorem 23, numbering of arXiv:2305.11833v1.
