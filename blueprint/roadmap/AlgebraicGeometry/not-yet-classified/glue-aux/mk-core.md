# Mk Core

Gluing data for schemes given by opens `V i j` of `U i` and transition maps
`t i j : V i j ⟶ V j i` such that `V i i` is all of `U i` (`V_id`), `t i i` is the identity
(`t_id`), `t i j` sends `V i j ∩ V i k` into `V j i ∩ V j k` (`t_inter`), and on
`V i j ∩ V i k` the two routes to `U k`, through `t i j` and `t j k` or through `t i k`, agree
(`cocycle`). This is the scheme analogue of `TopCat.GlueData.MkCore`.
