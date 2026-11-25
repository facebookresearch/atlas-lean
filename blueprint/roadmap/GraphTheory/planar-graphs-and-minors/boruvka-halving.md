# Component halving

Let `C` be a finite type of component labels and `f : C → C` a merging map such that every label `c` shares its image with a different label: for each `c` there is `d ≠ c` with `f d = f c`. Then the number of distinct images of `f` is at most half the number of labels: `2 · |f(C)| ≤ |C|`. In Borůvka's algorithm this bounds the number of components after one merging round.
