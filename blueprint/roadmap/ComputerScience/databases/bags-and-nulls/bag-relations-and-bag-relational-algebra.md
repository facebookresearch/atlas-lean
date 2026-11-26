# Bag relations and bag relational algebra

Let $A$ be a type of attributes, $D$ a type of values, and $S$ a finite set of attributes.
A tuple over $S$ is a partial assignment $t : A \to \operatorname{Option}(D)$ that is
**defined exactly on** $S$. Write $\operatorname{Tup}(S)$ for this type of tuples.
A bag relation on $S$ is a function $r : \operatorname{Tup}(S) \to \mathbb{N}$ with finite
support $\operatorname{supp}(r) = \{t : r(t) \ne 0\}$. Thus $r(t)$ is the multiplicity of $t$;
zero means the tuple is absent. Neither $A$ nor $D$ needs to be finite.

The positive algebra on these bags consists of the zero bag, the following operations, and the
set embedding below:

- **Selection.** For a condition $c$ whose attributes all lie in $S$, the result is a bag on $S$.
  At $t$ it has multiplicity $r(t)$ if $c$ is true on $t$, and $0$ otherwise. The conditions
  are built from truth, equality of an attribute with a constant, equality of two attributes,
  negation, and conjunction. A condition keeps or discards the entire multiplicity.
- **Projection.** If $T \subseteq S$, projection sends a bag on $S$ to a bag on $T$. At
  $u \in \operatorname{Tup}(T)$ its multiplicity is
  $\sum_{t \in \operatorname{supp}(r),\ t|_T = u} r(t)$, where $t|_T$ is restriction to $T$.
  In particular, distinct tuples that restrict to the same $u$ contribute to the same sum.
- **Natural join.** If $r$ is on $S$ and $s$ is on $T$, their join is on $S \cup T$ and has
  multiplicity $r(w|_S)\,s(w|_T)$ at $w \in \operatorname{Tup}(S \cup T)$.
  The two restrictions agree on the overlap and merge to $w$; they are the unique compatible
  pair with that merge. Pairs that disagree on any shared attribute do not contribute.
- **Union.** Two bags on the same schema $S$ give a bag on $S$ with multiplicity $r(t)+s(t)$
  at $t$. The empty bag is zero everywhere.
- **Renaming.** For a permutation $f : A \simeq A$, a bag $r$ on $S$ is sent to a bag on $f(S)$.
  At $u \in \operatorname{Tup}(f(S))$ the multiplicity is $r(u \circ f)$; equivalently, the
  value at attribute $a$ in each input tuple moves to $f(a)$ with no change of multiplicity.

Each result has finite support. Selection filters the support, projection takes its image, join
merges compatible pairs from the two supports, union takes their set union, and renaming maps the
support bijectively. A finite set relation whose members are all over $S$ embeds into the bags
on $S$ by giving its members multiplicity $1$ and every other tuple multiplicity $0$; taking the
support recovers the original set relation.

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, §3,
  Definition 3.2 and Proposition 3.3. The multiplicity formulas and closure under the operations
  are the specialization to the semiring $(\mathbb{N}, +, \cdot, 0, 1)$.
  <https://web.cs.ucdavis.edu/~green/papers/pods07.pdf>
