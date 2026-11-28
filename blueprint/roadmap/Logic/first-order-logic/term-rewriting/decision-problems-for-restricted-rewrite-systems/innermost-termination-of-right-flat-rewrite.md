# Innermost termination of right-flat rewrite systems is undecidable

Whether every innermost derivation of a finite term rewriting system terminates is undecidable even when all right-hand sides of rules have height at most one.

**Theorem (Barguñó, Godoy, Huntingford and Tiwari).** A rewrite step $s \to_{R, p} t$ at position $p$ is *innermost* if every proper subterm $s|_{p'}$ with $p' > p$ is irreducible, and a [term rewriting system](../../automated-deduction/term-rewriting-systems.md) is *innermost terminating* if it admits no infinite derivation consisting of innermost steps. A rule $l \to r$ is *right-flat* if $r$ has height at most $1$. Innermost termination of finite right-flat term rewriting systems, given together with their finite signature, is undecidable (Theorem 8.3 of the source, by a reduction from the Post correspondence problem).

For shallow, and hence flat, systems innermost termination is decidable, even modulo permutative theories (Section 5 of the source), and innermost termination of a right-flat system from a given term is decidable (Theorem 4.10); the undecidability concerns right-flat systems with arbitrary left-hand sides and all start terms.

## Depends on

- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

For an instance $\langle u_1, v_1\rangle, \ldots, \langle u_n, v_n\rangle$ of the Post correspondence problem, words are written as unary terms and $\epsilon$ is a constant; the system consists of the rules $f(x) \to g(x, x, x)$, $g(x, u_i(y), v_i(z)) \to h(x, y, z)$, $h(x, u_i(y), v_i(z)) \to h(x, y, z)$ and $h(x, \epsilon, \epsilon) \to f(x)$ for $1 \le i \le n$. All right-hand sides are flat. A term $f(w)$ in which $w$ can be read both as $u_{i_1} \cdots u_{i_k}$ and as $v_{i_1} \cdots v_{i_k}$, a solution, rewrites back to itself by innermost steps; the source states that the instance has a solution iff the system is not innermost terminating.

## Sources

- L. Barguñó, G. Godoy, E. Huntingford and A. Tiwari, "Termination of Rewriting with Right-Flat Rules Modulo Permutative Theories", *Logical Methods in Computer Science* 6(3), 2010, paper 8, <https://doi.org/10.2168/LMCS-6(3:8)2010>; read as arXiv:1006.0706v3, <https://arxiv.org/abs/1006.0706v3>: Section 2 (innermost steps, right-flat rules), Theorem 4.10, Section 5, and Section 8 (Theorem 8.3 and its proof).
