# Two-stage neurons compute exactly the positive Boolean functions

Let $x \in \{0,1\}^n$ be a binary input. A **two-stage neuron** with $m$ dendritic sub-units has non-negative weight vectors $w_1, \dots, w_m \in \mathbb{R}_{\ge 0}^n$, non-decreasing dendritic activation functions $g_1, \dots, g_m : \mathbb{R}_{\ge 0} \to \mathbb{R}_{\ge 0}$, and somatic threshold $\Theta$; its output is

$$y(x) = \mathbf{1}\Big[ \sum_{j=1}^{m} g_j(w_j \cdot x) \ge \Theta \Big].$$

A Boolean function $f$ is **positive** (monotone) if $x \le x'$ componentwise implies $f(x) \le f(x')$. A function $g$ is **supra-linear** on a set if $g(a + b) > g(a) + g(b)$ for at least one admissible pair, **sub-linear** if $g(a+b) < g(a) + g(b)$ for at least one pair, and **strictly** sub-linear (supra-linear) if it is sub-linear but not supra-linear (respectively the reverse). A **spiking** dendritic activation (zero below a threshold, a fixed height above it) is both supra- and sub-linear; a **saturating** activation (linear up to a ceiling, then flat) is strictly sub-linear.

**Lemma.** With non-negative weights and non-decreasing activations, $y$ is a positive Boolean function.

**Proposition (DNF construction).** With enough spiking sub-units, a two-stage neuron implements every positive Boolean function: one sub-unit per prime term of its complete positive disjunctive normal form.

**Proposition (CNF construction).** With enough sub-units that are spiking or saturating, a two-stage neuron implements every positive Boolean function: one sub-unit per prime clause of its complete positive conjunctive normal form.

**Proposition (impossibility).** A sub-unit with a strictly sub-linear activation cannot implement a conjunction (term) $x_{i_1} \wedge \dots \wedge x_{i_r}$ with $r \ge 2$; hence a neuron whose sub-units are all saturating cannot implement a function through its complete DNF.

In particular, passive (saturating) dendrites suffice for a single neuron to compute linearly non-separable positive functions, contrary to the view that dendritic spikes are needed.

## Expansion

Lemma: if $x \le x'$ then $w_j \cdot x \le w_j \cdot x'$ for every $j$, each $g_j$ preserves the order, the sum preserves it, and so does the Heaviside threshold. Every positive Boolean function has a unique complete positive DNF (disjunction of its prime implicants, all with uncomplemented variables) and a complete positive CNF. A term on $r$ variables is realized by a unit with unit weights on those variables and a step at $r$ (supra-linear: the unit fires only when all $r$ inputs are on); the soma then fires if any unit fires, an OR. A clause is realized by a unit with unit weights and a ceiling at $1$ (sub-linear: one active input already saturates it); the soma, with threshold equal to the number of clause units, computes their AND. For the impossibility, a unit implementing a term must give a sub-threshold value to each proper subset of the variables but a supra-threshold value to their union, which forces $g$ of a sum to exceed the sum of the values of the parts, a supra-linear pair; a strictly sub-linear $g$ has none.

## Sources

- R. D. Cazé, M. Humphries, B. Gutkin, "Passive dendrites enable single neurons to compute linearly non-separable functions", PLoS Computational Biology 9(2) (2013) e1002867, Eq. (2), Propositions 1–3 and Materials and Methods, Lemmas 1–3, <https://doi.org/10.1371/journal.pcbi.1002867>, PMCID PMC3585427.
