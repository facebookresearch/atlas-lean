# Haplotype likelihoods on variation graphs

When a reference population is stored as haplotype paths through a variation graph, structural variants, nested indels and cycles need not be forced onto linearly ordered sites. The Li–Stephens copying model extends to this setting with recombination at base-pair resolution: a haplotype's likelihood is a weighted count of recombination mosaics of reference paths, computable by a prefix dynamic program whose equivalence classes are enumerated with a graph positional Burrows–Wheeler index.

- [Li–Stephens recombination likelihood on variation graphs](li-stephens-recombination-likelihood-on-variation-graphs.md)
