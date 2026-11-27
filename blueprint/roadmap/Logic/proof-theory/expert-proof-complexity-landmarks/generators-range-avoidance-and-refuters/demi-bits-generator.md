# Demi-bits generators

A demi-bits generator is a stretching map $G:\{0,1\}^n\to\{0,1\}^m$ such that no small nondeterministic adversary rejects every output of $G$ while accepting a noticeable fraction of all $m$-bit strings. The notion is the nondeterministic analogue of a cryptographic hitting set generator.

Let $n<m$ be length parameters. A function $G:\{0,1\}^n\to\{0,1\}^m$ is an **$(s,\varepsilon)$-secure demi-bits generator** if there is no $\mathsf{NP}/\mathrm{poly}$ adversary $\mathrm{Adv}$ of size $s$ such that

$$
\Pr_{y\sim\{0,1\}^m}[\mathrm{Adv}(y)=1]\ge\varepsilon \quad\text{and}\quad \Pr_{x\sim\{0,1\}^n}[\mathrm{Adv}(G(x))=1]=0.
$$

When security holds against every $\mathsf{NP}/\mathrm{poly}$ adversary of polynomial size, $G$ is called an **$\varepsilon$-secure demi-bits generator** (or simply a demi-bits generator, with a constant $\varepsilon$), and a family $\{g_n\}$ is said to be secure against $\mathsf{NP}/\mathrm{poly}$. Security against uniform $\mathsf{NP}$ adversaries is defined in the same way, the adversary receiving the circuit of $G$ as an extra input when $G$ is non-uniform. Since an adversary may guess a proof and verify it, an $\varepsilon$-secure $G$ admits no efficient sound proof system proving "$y\notin\mathrm{Range}(G)$" for at least $\varepsilon 2^m$ strings $y$.

**Weak demi-bits generators.** $G$ is an **$(s,K)$-weak demi-bits generator** if there is no $\mathsf{NP}/\mathrm{poly}$ adversary $\mathrm{Adv}$ of size $s$ with

$$
\bigl|\{y\in\{0,1\}^m : \mathrm{Adv}(y)\text{ rejects}\}\bigr|<K \quad\text{and}\quad \Pr_{x\sim\{0,1\}^n}[\mathrm{Adv}(G(x))\text{ rejects}]=1.
$$

A $K$-weak demi-bits generator is the same as a $(1-K/2^m)$-secure one, and every injective $G$ is trivially a $2^n$-weak demi-bits generator.

**Against a fixed proof system.** Let $\mathcal P$ be a propositional proof system, let $G:\{0,1\}^n\to\{0,1\}^\ell$ with $\ell>n$ be computable by polynomial-size circuits (non-uniform advice allowed), and for $b\in\{0,1\}^\ell$ let $\tau_b(G)$ be a propositional formula encoding "$b\notin\mathrm{Range}(G)$". Then $G$ is a **demi-bits generator against $\mathcal P$** if for at least a $1/3$ fraction of $b\in\{0,1\}^\ell$, $\mathcal P$ has no polynomial-size proof of $\tau_b(G)$; it is a **proof complexity generator against $\mathcal P$** if this holds for every $b\in\{0,1\}^\ell$.

## Expansion

Rudich introduced demi-bits as cryptography against nondeterministic adversaries; his stronger notion of super-bits is the analogue of a pseudorandom generator, while demi-bits generators are the analogue of a hitting set generator. Demi-bits generators connect to natural proofs with nondeterministic constructivity: if the truth table generator, mapping a small circuit to its truth table, is a secure demi-bits generator, then no $\mathsf{NP}$-constructive large property certifies circuit lower bounds.

The two notions against a proof system differ only in quantifier strength: a demi-bits generator needs hard statements "$b\notin\mathrm{Range}(G)$" for an average $b$, a proof complexity generator for the best-case $b$. Candidate demi-bits generators with polynomial stretch, or with stretch $n^{1+\epsilon}$ and constant $\mathbb F_2$-degree, come from noisy-parity (LPN-style) generators and Goldreich's local generator.

## Depends on

- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Hanlin Ren, Yichuan Wang, Yan Zhong, "Hardness of Range Avoidance and Proof Complexity Generators from Demi-Bits", *ITCS* 2026, arXiv:2511.14061v2, https://arxiv.org/abs/2511.14061 (Definition 2.1, Assumptions 2.2 and 2.3, Section 3.1, Appendix B).
- Xin Li, Hanlin Ren, Yan Zhong, "Many Proof Complexity Generators Inside One Demi-Bits Generator", *FOCS* 2026, arXiv:2609.23228v1, https://arxiv.org/abs/2609.23228 (Definitions 2.1 and 2.2, Section 1.3).
