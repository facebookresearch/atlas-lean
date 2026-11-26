# Dendrite-AND needs a weight ratio of n − 1 in a linear threshold unit

For $n \ge 3$ binary inputs $X_1, \dots, X_n$, the dendrite-AND function is $f(X) = X_1 \wedge (X_2 \vee \dots \vee X_n)$: the output is active iff $X_1$ is active together with at least one other input. It is a positive linearly separable Boolean function. A linear threshold unit (LTU) with non-negative weights $w_1, \dots, w_n$ and threshold $\Theta$ outputs $1$ iff $\sum_i w_i X_i \ge \Theta$. A sub-linear threshold unit (SLTU) with $d$ dendrites has binary weights $w_{i,j} \in \{0, 1\}$ and outputs $1$ iff $\sum_{i=1}^d E\bigl(\sum_j w_{i,j}X_j\bigr) \ge \Theta$, where $E(y) = \min(y, 1)$ models dendritic saturation.

1. If an LTU with integer weights and threshold, whose smallest weight is one resolution unit $w_{\min} = 1$, implements the dendrite-AND, then $w_1 \ge n - 1$; the bound is attained by $w_1 = n - 1$, $w_2 = \dots = w_n = 1$, $\Theta = n$. (With real weights the same argument gives $w_1 > (n - 2)\,w_{\min}$.)
2. An SLTU with two dendrites and binary weights implements it: one dendrite receives $X_1$, the other receives $X_2, \dots, X_n$, and $\Theta = 2$.

Thus saturating dendrites let a neuron compute this linearly separable function with synaptic weights of the lowest possible resolution, which a point neuron cannot do.

## Expansion

The LTU must stay silent when $X_2, \dots, X_n$ are all active but $X_1$ is not, so $\Theta > w_2 + \dots + w_n \ge (n - 1)w_{\min}$, hence $\Theta \ge n$ for integer parameters with $w_{\min} = 1$; it must fire when $X_1$ and the weakest other input are active, so $w_1 + w_{\min} \ge \Theta$, giving $w_1 \ge n - 1$. For the SLTU, the second dendrite saturates at $1$ as soon as any of $X_2, \dots, X_n$ is active, so the somatic sum reaches $2$ exactly when $X_1$ and some other input are active. This complements the result that two-stage neurons compute exactly the positive Boolean functions, which concerns expressiveness rather than weight resolution.

## Sources

- R. D. Cazé and M. Stimberg, "Neurons with dendrites can perform linearly separable computations with low resolution synaptic weights", F1000Research 9 (2020) 1174 (version 3), <https://doi.org/10.12688/f1000research.26486.3>, PMCID PMC7848858. Definitions 1–5 and Proposition 1 (with the constructive SLTU of Figure 3B).
