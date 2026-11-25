# Finite chance tree

A finite chance tree with real utilities is built from:
- a leaf carrying a real utility;
- a max node or a min node over a list of subtrees;
- a chance node over a list of weighted subtrees $(p, t)$;
- an affine edge $(c, \gamma, t)$, standing for the value $c + \gamma\cdot(\text{value of } t)$, as when one MDP transition collects reward $c$ and discounts the continuation by $\gamma$.
