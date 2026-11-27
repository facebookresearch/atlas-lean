# Deduction modulo homeomorphic-embedded convergent rewrite systems is undecidable

Intruder deduction is undecidable for convergent term rewrite systems in which every right-hand side is homeomorphically embedded in its left-hand side, a class that includes theories beyond subterm convergent ones, such as blind signatures. For subterm convergent theories deduction is decidable in polynomial time.

**Setting.** A term rewrite system $R$ over a signature $\Sigma$ is *convergent* if it is terminating and confluent. The *homeomorphic embedding* $\trianglerighteq_{\mathrm{emb}}$ is the least relation on terms with $x \trianglerighteq_{\mathrm{emb}} x$ for variables, $f(s_1, \dots, s_n) \trianglerighteq_{\mathrm{emb}} f(t_1, \dots, t_n)$ if $s_i \trianglerighteq_{\mathrm{emb}} t_i$ for all $i$, and $f(s_1, \dots, s_n) \trianglerighteq_{\mathrm{emb}} t$ if $s_i \trianglerighteq_{\mathrm{emb}} t$ for some $i$; equivalently, it is the reflexive transitive closure of the rewrite relation of $\{ f(x_1, \dots, x_n) \to x_i \}$. $R$ is *homeomorphic-embedded* if $l \trianglerighteq_{\mathrm{emb}} r$ for every rule $l \to r$. The signature contains a countable set of free constants, including the names. For a frame $\phi = \nu\tilde{n}.\sigma$ ($\sigma$ a substitution with ground range, $\tilde{n}$ a finite set of names) and a ground term $t$, $t$ is *deduced* from $\phi$ modulo $R$, written $\phi \vdash_R t$, if $\zeta\sigma =_R t$ for some term $\zeta$ (a recipe) containing no name of $\tilde{n}$.

**Theorem (Bunch, Dwyer Satterfield, Erbatur, Marshall and Ringeissen).** The following problem is undecidable: given a homeomorphic-embedded convergent term rewrite system $R$ (part of the input), a frame $\phi$ and a ground term $t$, does $\phi \vdash_R t$ hold?

The paper derives the same undecidability for its larger class of graph-embedded convergent systems, and shows that deduction and static equivalence are decidable for its contracting convergent systems, a locally stable subclass of the graph-embedded ones that goes beyond subterm convergent systems. Abadi and Cortier had earlier proved deduction and static equivalence undecidable in general, also by a reduction from the Post correspondence problem; their rewrite system is not graph-embedded.

## Depends on

- [Frames and static equivalence](frames-and-static-equivalence.md)
- [Equational theories and convergent subterm theories](equational-theories-and-convergent-subterm-theories.md)
- [Term rewriting systems](../../../Logic/first-order-logic/automated-deduction/term-rewriting-systems.md)

## Proof depends on

- [MPCP is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-mpcp.md)

## Expansion

The reduction is from the modified Post correspondence problem over $\{a, b\}$ with prescribed suffixes $\alpha_0, \beta_0$. Strings become towers of unary symbols $a, b$. For each pair $(\alpha_i, \beta_i)$ there is a *block rule* $f(\tilde{\alpha}_i(x), g_i(y), \tilde{\beta}_i(z), \mathit{unlocked}(k)) \to f(x, y, z, \mathit{unlocked}(k))$, and one *unlock rule* $f(x, y, x, \mathit{locked}(\mathit{unlocked}(z))) \to f(x, y, x, \mathit{unlocked}(z))$; the symbols $g_i$ and $\mathit{locked}$ rule out critical pairs, so the system is convergent, and each right-hand side is embedded in its left-hand side. With $\phi = \nu\{c, e\}.\{x \mapsto \tilde{\alpha}_0(c),\ y \mapsto \tilde{\beta}_0(c),\ z \mapsto \mathit{locked}(\mathit{unlocked}(e))\}$, the term $f(c, d, c, \mathit{unlocked}(e))$ is deducible exactly when the instance has a solution: the unlock rule fires only when the two strings in the recipe agree, and the block rules then strip matching pairs, whose indices are recorded by the $g_i$.

## Sources

- Carter Bunch, Saraid Dwyer Satterfield, Serdar Erbatur, Andrew M. Marshall and Christophe Ringeissen, "Knowledge Problems in Protocol Analysis: Extending the Notion of Subterm Convergent", Logical Methods in Computer Science 22(2), Article 15, 2026, <https://doi.org/10.46298/lmcs-22(2:15)2026>; Lemma 4.1 (main statement), Corollary 4.3 (graph-embedded systems), Remark 4.4 and Definition 2.2 (homeomorphic embedding) of arXiv:2401.17226v5, <https://arxiv.org/abs/2401.17226v5>.
- Martín Abadi and Véronique Cortier, "Deciding knowledge in security protocols under equational theories", Theoretical Computer Science 367(1–2), pp. 2–32, 2006, <https://doi.org/10.1016/j.tcs.2006.08.032>; the earlier undecidable theory, not read: the clause rests on Remark 4.4 of the version read of the first source above, which recalls it.
