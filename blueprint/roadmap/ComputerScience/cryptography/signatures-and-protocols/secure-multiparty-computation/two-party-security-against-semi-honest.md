# Two-party security against semi-honest adversaries

A *semi-honest* party follows the protocol properly, tossing fair coins and sending messages according to its program, except that it keeps a record of its internal coin tosses and of all messages it receives. Let $f : \{0,1\}^* \times \{0,1\}^* \to \{0,1\}^* \times \{0,1\}^*$ be a functionality with components $f(x, y) = (f_1(x, y), f_2(x, y))$, and let $\Pi$ be a two-party protocol that computes $f$, in the sense that its output distribution on inputs $(x, y)$, with honest or semi-honest parties, is identical to that of $f(x, y)$. The *view* of the first party in an execution on $(x, y)$ is $\mathrm{view}_1(x, y) = (x, r, m_1, \dots, m_t)$, where $r$ is the outcome of its internal coin tosses and $m_i$ is the $i$-th message it receives, and similarly $\mathrm{view}_2(x, y) = (y, r, m_1, \dots, m_t)$ for the second party; the outputs $\mathrm{output}_1(x, y)$ and $\mathrm{output}_2(x, y)$ are determined by the views, and $\mathrm{output}(x, y)$ is the pair, all defined from the same random execution.

The protocol $\Pi$ *privately computes* $f$ if there are probabilistic polynomial-time algorithms $S_1$ and $S_2$ such that, over pairs $x, y$ with $|x| = |y|$,

$$\bigl\{(S_1(x, f_1(x, y)),\ f(x, y))\bigr\}_{x, y} \stackrel{c}{\equiv} \bigl\{(\mathrm{view}_1(x, y),\ \mathrm{output}(x, y))\bigr\}_{x, y}, \qquad \bigl\{(S_2(y, f_2(x, y)),\ f(x, y))\bigr\}_{x, y} \stackrel{c}{\equiv} \bigl\{(\mathrm{view}_2(x, y),\ \mathrm{output}(x, y))\bigr\}_{x, y},$$


where $\stackrel{c}{\equiv}$ is computational indistinguishability by non-uniform families of polynomial-size circuits. For a deterministic functionality it suffices that $\{S_i(\cdot, f_i(x, y))\}$ be computationally indistinguishable from $\{\mathrm{view}_i(x, y)\}$ alone, with $S_1$ given $x$ and $S_2$ given $y$.

## Depends on

- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- O. Goldreich, *Foundations of Cryptography*, vol. 2: Basic Applications, Cambridge University Press, 2004; draft chapter "General Protocols", posted version 3.2, 2003, <https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.pdf>, Section 7.2.2 and Definition 7.2.1
