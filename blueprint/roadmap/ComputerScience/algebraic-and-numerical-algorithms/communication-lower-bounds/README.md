# Communication lower bounds

Moving data between levels of a memory hierarchy, or between processors, costs far more time and energy than arithmetic, so the cost of an algorithm is also measured by the number of words it moves. On a sequential machine with a fast memory of $M$ words, classical matrix multiplication of $n \times n$ matrices must move $\Omega(n^3/\sqrt{M})$ words between fast and slow memory (Hong and Kung, 1981; Irony, Toledo and Tiskin, 2004), and blocked or recursive algorithms attain this bound. Ballard, Demmel, Holtz and Schwartz (2011) showed that the same bound, $\Omega(\#\text{multiply-adds}/\sqrt{M})$, holds for every computation shaped like matrix multiplication: dense and sparse LU, Cholesky and $LDL^T$ factorisations, among others. Dividing by the largest message size $M$ gives a lower bound on the number of messages.

The argument cuts the execution into segments of $M$ loads and stores, bounds by the [discrete Loomis–Whitney inequality](../../../Combinatorics/extremal-set-theory/loomis-whitney-and-brascamp-lieb-inequalities/card-sq-le-card-mul-card-mul-card.md) the number of multiply-adds a segment can perform with the at most $4M$ operands of each kind available to it, and counts segments.

- [Bandwidth lower bound, segment-counting form](card-div-sub-le-words.md)
- [Evaluations per segment](card-le-of-card-image-le.md)
- [Communication lower bound for classical matrix multiplication](matmul-card-div-sub-le-words.md)
- [Parallel bandwidth lower bound](exists-card-div-sub-le-words-of-parallel.md)

## Related topics

- [Matrix multiplication algorithms](../matrix-multiplication-algorithms/README.md): the classical and recursive algorithms whose communication these bounds limit.
- [Strassen algorithm](../strassen-algorithm/README.md): it does not evaluate every product $A(i,k) B(k,j)$, so it lies outside this model; its communication bounds need other (graph expansion) arguments.
- [Loomis–Whitney and Brascamp–Lieb inequalities](../../../Combinatorics/extremal-set-theory/loomis-whitney-and-brascamp-lieb-inequalities/README.md): the geometric inequalities behind the per-segment bound, and their generalisation to arbitrary affine array subscripts.
