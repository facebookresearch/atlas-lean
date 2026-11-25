# Continuing symbolic execution on terminal leaves only

A leaf of bounded symbolic execution is either a terminal leaf $\operatorname{done}(p)$ or a cutoff leaf $\operatorname{cut}(p)$ carrying a symbolic path $p$. For a continuation $h$ from paths to lists of leaves, binding $h$ over a leaf gives $h(q)$ for $\operatorname{done}(q)$ and the one-element list $[\operatorname{cut}(q)]$ for $\operatorname{cut}(q)$.
