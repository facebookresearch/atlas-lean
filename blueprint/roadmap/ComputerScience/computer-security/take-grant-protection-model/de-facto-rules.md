# De facto rules

Let $G_0$ be a [protection graph](take-grant-protection-graphs.md). Besides its explicit edges, a graph may carry *implicit* edges labelled $r$, which record a
potential flow of information that is not an authority; the de jure rules do not act on implicit edges. Each *de facto rule* applies to three distinct vertices
$x, y, z$ and adds an implicit edge from $x$ to $z$ labelled $r$:

- **Post** ("$z$ posts to $x$ through $y$"): $x$ and $z$ are subjects, the edge from $x$ to $y$ has $r$ in its label and the edge from $z$ to $y$ has $w$ in its label;
- **Pass** ("$y$ passes from $z$ to $x$"): $y$ is a subject, the edge from $y$ to $x$ has $w$ in its label and the edge from $y$ to $z$ has $r$ in its label;
- **Spy** ("$x$ spies on $z$ using $y$"): $x$ and $y$ are subjects, the edge from $x$ to $y$ has $r$ in its label and the edge from $y$ to $z$ has $r$ in its label;
- **Find** ("$x$ finds from $z$ through $y$"): $y$ and $z$ are subjects, the edge from $y$ to $x$ has $w$ in its label and the edge from $z$ to $y$ has $w$ in its label.

## Depends on

- [Take–grant protection graphs](take-grant-protection-graphs.md)

## Sources

- M. Bishop, "Conspiracy and information flow in the take-grant protection model", *Journal of Computer Security* 4(4):331–359, 1996, author copy at <http://nob.cs.ucdavis.edu/bishop/papers/1996-jcs/tgconsp.pdf>: Section 2, implicit edges and the de facto rules post, pass, spy and find (introduced in M. Bishop and L. Snyder, "The transfer of information and authority in a protection system", *Proceedings of the 7th ACM Symposium on Operating Systems Principles*, 1979).
