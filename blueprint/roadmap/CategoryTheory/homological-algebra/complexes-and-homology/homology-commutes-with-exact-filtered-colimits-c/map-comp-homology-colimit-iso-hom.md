# Homology-colimit comparison preserves diagram injections

Let `C` be abelian with colimits of shape `J`, where `J` is
any category, and suppose `colim : (J → C) → C` preserves homology.
Let `c` be any complex shape and `K : J → HomologicalComplex C c`. For `j : J`, taking homology of `K_j → colim K` and then
the forward comparison gives the injection
`H_i(K_j) → colim_l H_i(K_l)`.
