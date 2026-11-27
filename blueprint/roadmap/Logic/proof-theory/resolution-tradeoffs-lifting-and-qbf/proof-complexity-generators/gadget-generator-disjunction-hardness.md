# The gadget generator is the disjunction-hardest proof complexity generator

For sufficiently strong proof systems, if any polynomial-time generator is $\bigvee$-hard, then the gadget generator built from the circuit value function on circuits described by strings of length $k^2$ is $\bigvee$-hard, and hence hard, as well.

Given a polynomial-time $f : \{0,1\}^\ell \times \{0,1\}^k \to \{0,1\}^{k+1}$, the **gadget generator** $\mathrm{Gad}_f : \{0,1\}^n \to \{0,1\}^{n+1}$, with $n := \ell + k(\ell + 1)$, reads its input as $v \in \{0,1\}^\ell$ and $u^1, \dots, u^{\ell+1} \in \{0,1\}^k$ and outputs the concatenation of the $\ell + 1$ strings $w^s := f(v, u^s) \in \{0,1\}^{k+1}$. Take $f = \mathrm{CV}_{k^2, k}$, the circuit value function evaluating on $u$ the circuit with $k$ inputs and $k+1$ outputs described by the string $v$ of length $\ell = k^2$; $\ell$ is the size of the description, not of the circuit.

**Theorem.** Let $P$ be a propositional proof system that simulates extended Frege and for which there is $c \ge 1$ such that substituting constants for atoms in a tautology $\sigma$ gives $\sigma'$ with $s_P(\sigma') \le s_P(\sigma)^c$, and $s_P(\beta) \le (s_P(\alpha) + s_P(\alpha \to \beta))^c$ for all $\alpha, \beta$. If some polynomial-time function $g$ stretching inputs of size $n$ to size $m(n) > n$ is $\bigvee$-hard for $P$, then the gadget generator based on $\mathrm{CV}_{k^2,k}$ is $\bigvee$-hard, and hence hard, for $P$.

## Expansion

Without loss of generality $m(n) = n + 1$. Let $C_k$ be a canonical polynomial-size circuit computing $g_k$, encoded by a string $\lceil C_k \rceil$ of size $\ell \le k^a$. Claim 1: the gadget generator based on $\mathrm{CV}_{k^a, k}$ is $\bigvee$-hard. Its $\tau$-formula for $b = (b^1, \dots, b^t)$ is a disjunction, $t = k^a + 1$, of $\tau$-formulas for $\mathrm{CV}_{k^a,k}$ and the blocks $b^i$; substituting $v := \lceil C_k \rceil$ and using polynomial-size extended Frege proofs of $\mathrm{CV}_{k^a,k}(\lceil C_k \rceil, u) = C_k(u)$ turns any proof of a disjunction for the gadget generator into a polynomially longer $P$-proof of a disjunction of $\tau$-formulas for $g$. Claim 2: the generator of Claim 1 runs in time $O(k^{2a}) \le n^{2-\delta}$, so the same construction applied to it in place of $g$ yields $\bigvee$-hardness of the generator based on $\mathrm{CV}_{k^2,k}$. Hardness follows since $\bigvee$-hardness implies hardness. Gadget generators are known to be hard for many proof systems with super-polynomial lower bounds, and the source proposes this one as a candidate for the conjecture that some generator is hard for all proof systems.

## Depends on

- [Proof complexity generators and their tau-formulas](proof-complexity-generators.md)

## Proof depends on

None.

## Sources

- J. Krajíček, "On the existence of strong proof complexity generators", *Bulletin of Symbolic Logic*, 2023, doi:10.1017/bsl.2023.40, arXiv:2208.11642v4 (Section 4, the definition of gadget generators and Theorem 4.1).
