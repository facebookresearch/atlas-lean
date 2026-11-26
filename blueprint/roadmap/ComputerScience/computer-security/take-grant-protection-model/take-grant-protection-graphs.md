# Take–grant protection graphs

A *protection graph* is a finite directed graph whose vertices are of two types, *subjects* (active entities) and *objects* (passive entities), and whose
edges are labelled by nonempty subsets of the set of rights $R = \{r, w, t, g\}$ (read, write, take, grant); there is at most one edge from a vertex $a$ to a vertex $b$,
and $\alpha \in \lambda(a, b)$ means that $a$ has the right $\alpha$ to $b$. The *de jure rules* rewrite a protection graph $G$ into a graph $G'$:

- **Take.** If $x, y, z$ are distinct vertices, $x$ is a subject, the edge from $x$ to $y$ contains $t$, the edge from $y$ to $z$ is labelled $\beta$ and $\alpha \subseteq \beta$, then
  $G'$ adds $\alpha$ to the label of the edge from $x$ to $z$ ("$x$ takes ($\alpha$ to $z$) from $y$").
- **Grant.** If $x, y, z$ are distinct vertices, $x$ is a subject, the edge from $x$ to $y$ contains $g$, the edge from $x$ to $z$ is labelled $\beta$ and $\alpha \subseteq \beta$, then
  $G'$ adds $\alpha$ to the label of the edge from $y$ to $z$ ("$x$ grants ($\alpha$ to $z$) to $y$").
- **Create.** If $x$ is a subject and $\alpha \subseteq R$, then $G'$ adds a new vertex $n$, a subject or an object, and an edge from $x$ to $n$ labelled $\alpha$.
- **Remove.** If $x$ is a subject, the edge from $x$ to $y$ is labelled $\beta$ and $\alpha \subseteq R$, then $G'$ replaces the label by $\beta \setminus \alpha$, deleting the edge
  when the label becomes empty.

We write $G \vdash^* G'$ when $G'$ arises from $G$ by finitely many rule applications. Only subjects invoke rules; the vertex $y$ in Take and Grant may be a subject
or an object.

## Sources

- M. Bishop and L. Snyder, *The Transfer of Information and Authority in a Protection System*, Research Report 166, Department of Computer Science, Yale University, July 1979, <http://nob.cs.ucdavis.edu/~bishop/notes/1979-yalecs-166/yale-166.pdf>: Section 2 (protection graphs, p. 6) and Section 4 (the rules Take, Grant, Create and Remove, pp. 16–17).
