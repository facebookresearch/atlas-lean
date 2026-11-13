# FindSIS procedure for sufficient input subsets

`FindSIS`: un-mask features in reverse order of masking (start from `∅`) and return the
first set on which the prediction reaches the threshold, or `none`. The paper's procedure does
not test `∅` itself; the two agree whenever `g ∅ < τ`, the case the paper considers.
