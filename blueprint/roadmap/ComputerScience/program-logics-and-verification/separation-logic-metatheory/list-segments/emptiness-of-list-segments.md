# Emptiness of list segments

For [list segments](list-segment-predicate.md), equal endpoints $i = j$ alone do not force $\alpha = \epsilon$: since $i_n$ is unconstrained in the unfolding, $\mathrm{list}\ \alpha\ (i, i)$ may hold for a cyclic segment of any length. Emptiness is determined when $j$ is separated from the segment:

$$\mathrm{list}\ \alpha\ (i, j) \ast (j \mapsto -) \Rightarrow (i = j \Leftrightarrow \alpha = \epsilon), \qquad \mathrm{list}\ \alpha\ (i, j) \ast \mathrm{list}\ \beta\ (j, \mathbf{nil}) \Rightarrow (i = j \Leftrightarrow \alpha = \epsilon).$$

## Depends on

- [List segment predicate](list-segment-predicate.md)

## Sources

- J. C. Reynolds, "Separation logic: a logic for shared mutable data structures", *Proceedings of the 17th Annual IEEE Symposium on Logic in Computer Science (LICS 2002)*, IEEE, 2002, author copy <https://www.cs.cmu.edu/~jcr/seplogic.pdf>, Section 5.
