# Weakening a simply typed term

For a term $t$ of type $A$ in a context $\Gamma$ and a
simple type $B$, write $B :: \Gamma$ for the context obtained by prepending $B$ to $\Gamma$. The
weakening of $t$ is the term of type $A$ in the context $B :: \Gamma$ obtained by renaming $t$
along the renaming that sends each variable of $\Gamma$ to its successor in $B :: \Gamma$.
