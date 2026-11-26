# Composition laws for list segments

For [list segments](list-segment-predicate.md) the following equivalences hold in every state:

$$\mathrm{list}\ a\ (i, j) \iff i \mapsto a, j,$$

$$\mathrm{list}\ (\alpha \cdot \beta)\ (i, k) \iff \exists j.\ \mathrm{list}\ \alpha\ (i, j) \ast \mathrm{list}\ \beta\ (j, k),$$

$$\mathrm{list}\ (\alpha \cdot b)\ (i, k) \iff \exists j.\ \mathrm{list}\ \alpha\ (i, j) \ast (j \mapsto b, k).$$

The second, the composition law, is proved by structural induction on $\alpha$.

## Depends on

- [List segment predicate](list-segment-predicate.md)

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 5.
