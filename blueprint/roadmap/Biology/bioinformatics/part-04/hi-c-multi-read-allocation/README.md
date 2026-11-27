# Hi-C multi-read allocation

Hi-C read pairs whose ends align to several genomic locations are usually discarded, which depletes contacts in repetitive regions. Treating each read pair's true bin-pair origin as a latent multinomial draw with a distance-informed Dirichlet prior turns allocation of multi-reads into an EM problem whose posterior probabilities assign each multi-read to its most likely origin.

- [Dirichlet–multinomial EM for multi-mapping Hi-C read pairs](dirichlet-multinomial-em-for-multi-mapping-hi-c-read-pairs.md)
