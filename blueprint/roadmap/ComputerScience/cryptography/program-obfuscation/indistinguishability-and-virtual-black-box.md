# Indistinguishability and virtual black-box obfuscation

A probabilistic algorithm $\mathcal{O}$ is a *(circuit) obfuscator* for a collection $\mathcal{F}$ of circuits if the following hold.

- *Functionality*: for every circuit $C \in \mathcal{F}$, the string $\mathcal{O}(C)$ describes a circuit that computes the same function as $C$.
- *Polynomial slowdown*: there is a polynomial $p$ such that $|\mathcal{O}(C)| \le p(|C|)$ for every $C \in \mathcal{F}$.
- *Virtual black-box property*: for every probabilistic polynomial-time algorithm $A$ there are a probabilistic polynomial-time oracle algorithm $S$ and a negligible function $\alpha$ such that for every $C \in \mathcal{F}$,

    $$\bigl|\Pr[A(\mathcal{O}(C)) = 1] - \Pr[S^{C}(1^{|C|}) = 1]\bigr| \le \alpha(|C|).$$


The obfuscator is *efficient* if it runs in polynomial time, and when $\mathcal{F}$ is not specified it is the collection of all circuits. An *indistinguishability obfuscator* is defined in the same way, except that the virtual black-box property is replaced by

- *indistinguishability*: for every probabilistic polynomial-time algorithm $A$ there is a negligible function $\alpha$ such that for any two circuits $C_1, C_2$ that compute the same function and have the same size $k$, $\bigl|\Pr[A(\mathcal{O}(C_1)) = 1] - \Pr[A(\mathcal{O}(C_2)) = 1]\bigr| \le \alpha(k)$.

Inefficient indistinguishability obfuscators exist: map $C$ to the lexicographically first circuit of size $|C|$ that computes the same function.

## Depends on

- [Efficient adversaries](../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- B. Barak, O. Goldreich, R. Impagliazzo, S. Rudich, A. Sahai, S. Vadhan and K. Yang, "On the (im)possibility of obfuscating programs", *Journal of the ACM* 59(2), Article 6, 2012, <https://www.boazbarak.org/Papers/obfuscate.pdf>, Definition 2.2, Definition 7.1 and Proposition 7.2
