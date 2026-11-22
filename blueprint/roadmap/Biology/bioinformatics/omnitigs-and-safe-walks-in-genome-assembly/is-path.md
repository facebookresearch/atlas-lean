# Path in a directed multigraph

A sequence of edges $e_0, \dots, e_\ell$ is a path if it is a nonempty [walk](is-walk.md), the targets $\mathrm{tgt}(e_0), \dots, \mathrm{tgt}(e_\ell)$ are pairwise distinct, and $\mathrm{src}(e_0)$ is none of $\mathrm{tgt}(e_0), \dots, \mathrm{tgt}(e_{\ell-1})$: its nodes are distinct except that the first and last may coincide.
