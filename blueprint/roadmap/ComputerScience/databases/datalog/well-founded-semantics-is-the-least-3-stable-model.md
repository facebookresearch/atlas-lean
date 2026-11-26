# The well-founded semantics is the least 3-stable model

Let $P$ be a Datalog program with negation and let $\bot$ be the 3-valued instance in which every fact is false.
Define $I_0 = \bot$ and $I_{i+1} = \mathrm{conseq}_P(I_i)$. In the pointwise truth order $0 < \tfrac12 < 1$, the even-indexed instances form an
increasing and the odd-indexed instances a decreasing sequence; let $I_*$ and $I^*$ be their limits, and $I_{**}$
the 3-valued instance whose true facts are those true in $I_*$ and whose false facts are those false in $I^*$. Then
$I_{**}$ is a 3-stable model of $P$ and equals the well-founded semantics $P^{\mathrm{wf}}$ of $P$; in particular every
Datalog program with negation has a 3-stable model, and its well-founded semantics is contained in every 3-stable
model.

## Depends on

- [3-stable models of Datalog programs with negation](three-valued-stable-models.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the alternating fixpoint construction, Example 15.3.8 and Theorem 15.3.9 (pp. 390–393).
