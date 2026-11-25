# Probability of a set of sequences under independent draws

For a function $Q : \alpha \to \mathbb R$ on a finite alphabet and a set $S$ of sequences of length $n$, put

$$Q^n(S) = \sum_{x \in S} \prod_{i<n} Q(x_i).$$

When $Q$ is a probability vector this is the probability that $n$ independent draws from $Q$ form a sequence in
$S$. No measure on $\alpha^n$ is involved: $Q$ is an arbitrary real function, and the results using $Q^n$ state
their hypotheses on $Q$ (nonnegativity, sometimes positivity on a support) explicitly.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Section II (the notation $Q^n(\mathbf x)$ for $n$ independent drawings from $Q$).
