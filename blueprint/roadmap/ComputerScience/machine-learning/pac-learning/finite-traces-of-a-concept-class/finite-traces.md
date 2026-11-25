# Traces of a finite list of hypotheses

Let $\alpha$ have decidable equality, let $H = [h_1, \dots, h_k]$ be a finite list of hypotheses $h_j : \alpha \to \{\text{true},\text{false}\}$ and $s \subseteq \alpha$ a finite sample. The finite traces of $H$ on $s$ are the set of distinct positive subsets

$$\{\, \{x \in s : h_j(x) = \text{true}\} : j = 1, \dots, k \,\} ,$$

each a subset of $s$; repeated traces are counted once. The construction is computable: it decides only equality of sample points, never equality of functions.
