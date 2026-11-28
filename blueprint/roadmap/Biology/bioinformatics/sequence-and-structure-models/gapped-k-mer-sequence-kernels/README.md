# Gapped k-mer sequence kernels

Regulatory DNA sequences such as enhancers are recognized by short, degenerate transcription-factor binding motifs. Counting contiguous $k$-mers becomes sparse and noisy as $k$ grows; counting gapped $k$-mers (words of length $l$ with only $k$ informative positions) keeps the features robust, and the induced string kernel for support vector machines can be evaluated from mismatch counts between pairs of $l$-mers without enumerating the feature space.

- [Gapped k-mer kernel and its mismatch-profile formula](gapped-k-mer-kernel-and-mismatch-profile.md)
