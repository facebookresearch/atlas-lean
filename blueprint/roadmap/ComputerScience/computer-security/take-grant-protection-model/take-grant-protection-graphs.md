# Take–grant protection graphs

A *protection graph* is a finite directed graph whose vertices are *subjects* (active entities) or *objects* (passive entities), with at most one edge from a vertex
$a$ to a vertex $b$, labelled by a nonempty subset $\lambda(a, b)$ of a finite set of rights $R \supseteq \{r, w, t, g\}$ (read, write, take, grant). An empty label means
that there is no edge: adding rights $\alpha$ to the label of a missing edge creates the edge when $\alpha \ne \emptyset$, and adding $\emptyset$ changes nothing. The
*de jure rules* rewrite a protection graph $G_0$ into a graph $G_1$:

- **Take.** If $x, y, z$ are distinct vertices, $x$ is a subject, the edge from $x$ to $y$ has $t$ in its label, the edge from $y$ to $z$ is labelled $\beta$ and
  $\alpha \subseteq \beta$, then $G_1$ adds $\alpha$ to the label of the edge from $x$ to $z$ ("$x$ takes ($\alpha$ to $z$) from $y$").
- **Grant.** If $x, y, z$ are distinct vertices, $x$ is a subject, the edge from $x$ to $y$ has $g$ in its label, the edge from $x$ to $z$ is labelled $\beta$ and
  $\alpha \subseteq \beta$, then $G_1$ adds $\alpha$ to the label of the edge from $y$ to $z$ ("$x$ grants ($\alpha$ to $z$) to $y$").
- **Create.** If $x$ is a subject and $\alpha \subseteq R$, then $G_1$ adds a new vertex $y$, a subject or an object, and adds $\alpha$ to the label of the edge from $x$ to
  $y$ ("$x$ creates ($\alpha$ to new vertex) $y$"); for $\alpha = \emptyset$ the new vertex has no incoming edge.
- **Remove.** If $x$ and $y$ are distinct vertices, $x$ is a subject, the edge from $x$ to $y$ is labelled $\beta$ and $\alpha \subseteq R$, then $G_1$ replaces the label by
  $\beta \setminus \alpha$, deleting the edge when the label becomes empty ("$x$ removes ($\alpha$ to) $y$").

We write $G_0 \vdash^* G_n$ when $G_n$ arises from $G_0$ by finitely many rule applications.

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, the protection graph and the de jure rules take, grant, create and remove. The source draws each rule with an edge labelled $\alpha$; the empty-label convention above makes Create and Remove total on graphs with nonempty labels.
