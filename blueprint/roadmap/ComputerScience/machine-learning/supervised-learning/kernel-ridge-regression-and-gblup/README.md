# Kernel ridge regression and GBLUP

- [Positive definiteness of the GBLUP matrix](pos-def-mul-transpose-add.md)
- [Push-through identity for ridge regression](transpose-mul-add-inv-mul-transpose.md)
- [RR-BLUP = GBLUP (fitted values)](mul-ridge-hat-eq-gblup-hat.md)
- [Ridge marker effects are back-solved from GBLUP](ridge-estimate-eq.md)
- [RR-BLUP = GBLUP (predictions)](mul-vec-ridge-estimate.md)

## The Gaussian-process view

- [Linear marker kernel on genotype vectors](marker-kernel.md)
- [Formula for the linear marker kernel](marker-kernel-apply.md)
- [Kernel matrix of the marker kernel](kernel-matrix-marker-kernel.md)
- [Positive semidefiniteness of the marker kernel matrix](kernel-matrix-marker-kernel-pos-semidef.md)
- [GP posterior mean = GBLUP](gp-mean-marker-kernel.md)
- [GP posterior mean = RR-BLUP](gp-mean-marker-kernel-mul-vec.md)
- [The GBLUP posterior](cond-distrib-marker-kernel.md)

## The RKHS view

- [Kernel ridge regression = GBLUP = RR-BLUP](kernel-ridge-fit-eq-mul-vec-ridge-estima.md)

## Related topics

- [Positive-definite kernels](../../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): Aronszajn's theorem, which kernels are inner products of features.
- [Representer theorem](../../../../Analysis/hilbert-spaces/representer-theorem/README.md): kernel ridge regression over the whole reproducing kernel Hilbert space.
- [Random Fourier features](../random-fourier-features/README.md): an explicit random feature map that approximates a shift-invariant kernel, so that kernel methods can be run as linear ones on the features.
