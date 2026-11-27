# Weak orders without ties are strict total orders

Let $\succsim$ be a weak order (a rational preference relation) on a type $\alpha$: complete ($a \succsim b$ or $b \succsim a$ for all $a, b$) and transitive. Its strict part, $a \succ b$ when $a \succsim b$ and not $b \succsim a$, is irreflexive and transitive. If $\succsim$ has no ties between distinct elements ($a \succsim b$ and $b \succsim a$ imply $a = b$), then $\succ$ is a strict total order and $a \succsim b$ holds exactly when $a = b$ or $a \succ b$. Conversely, for every strict total order $\succ$, the relation \"$a = b$ or $a \succ b$\" is a weak order without ties whose strict part is $\succ$.

Proof. Irreflexivity of $\succ$ is immediate. If $a \succ b$ and $b \succ c$ then $a \succsim c$ by transitivity, and $c \succsim a$ would give $c \succsim b$, contradicting $b \succ c$. Without ties, for $a \ne b$ completeness gives $a \succsim b$ or $b \succsim a$ and not both, which is $a \succ b$ or $b \succ a$; and $a \succsim b$ with $a \ne b$ excludes $b \succsim a$, so $a \succ b$. For the converse, reflexivity gives completeness on equal elements, totality of $\succ$ gives it on distinct ones, transitivity follows from that of $\succ$, and asymmetry of $\succ$ excludes ties.

## Depends on

- [Strict total order](strict-total-order.md): strict total orders.
- [Rational preference relation](../../../Economics/choice-and-utility/preference-relations-and-choice/preference.md): rational (complete and transitive) preference relations.
- [Strict part of a rational preference](../../../Economics/choice-and-utility/preference-relations-and-choice/strict-pref-2.md): the strict part of a rational preference.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
