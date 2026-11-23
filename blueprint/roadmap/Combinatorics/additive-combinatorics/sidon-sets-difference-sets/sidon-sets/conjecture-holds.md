# Large Sidon sets have many isolated sums

For every natural number $M \ge 1$ there is a
natural number $K$ such that every finite Sidon set $A$ of natural numbers with at least $K$
elements has at least $M$ isolated elements in its sumset $A + A = \{x + y : x, y \in A\}$. Here
$A$ is a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$,
and an element $s$ of $A + A$ is isolated when $s + 1 \notin A + A$ and either $s = 0$ or
$s - 1 \notin A + A$.

This answers Erdős Problem 152 affirmatively: Tsoukalas et al. show that
every Sidon set $A$ of $n$ natural numbers has at least $(n^2 - 100n - 16)/16$ isolated elements
in $A + A$.

## Sources

- George Tsoukalas, Anton Kovsharov, Sergey Shirobokov, Anja Surina, Moritz Firsching, Gergely Bérczi, Francisco J. R. Ruiz, Arun Suggala, Adam Zsolt Wagner, Eric Wieser, Lei Yu, Aja Huang, Miklós Z. Horváth, Andrew Ferraiuolo, Henryk Michalewski, Edward Lockhart, Codrut Grosu, Thomas Hubert, Matej Balog, Pushmeet Kohli and Swarat Chaudhuri, *Advancing Mathematics Research with AI-Driven Formal Proof Search*, arXiv:2605.22763 (2026), appendix proof of Erdős Problem #152, https://arxiv.org/abs/2605.22763. The paper reports that its AI agent, AlphaProof Nexus, found this result with a Lean proof, https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/ErdosProblems/erdos_152.lean.
