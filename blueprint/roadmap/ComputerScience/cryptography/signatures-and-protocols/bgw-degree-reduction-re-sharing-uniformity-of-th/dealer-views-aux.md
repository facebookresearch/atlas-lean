# Joint subshare matrix over a list of dealers

Let `Party` have decidable equality, let `I` be a coalition and let `view i`
be a distribution on `I → F` for each dealer `i`. Starting from a matrix `g :
Party → I → F`, `dealerViewsAux view l g` processes the dealers of the list
`l` in order: each dealer `i` draws an independent view from `view i` and
overwrites row `i`. For the empty list it is the point mass at `g`.
