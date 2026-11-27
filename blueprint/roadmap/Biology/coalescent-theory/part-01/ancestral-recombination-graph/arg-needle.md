# ARG-Needle

ARG-Needle (Zhang, Biddanda, Gunnarsson, Cooper and Palamara 2023) builds an ancestral recombination graph by threading one haploid sample at a time onto the graph of the samples already added. For each new sample it (1) shortlists candidate close relatives among the threaded samples by genotype hashing, matching "words" of the genome exactly; (2) estimates the pairwise coalescence times between the new sample and each candidate along the genome with ASMC, a coalescent hidden Markov model; and (3) forms a threading instruction that gives, at each position, the closest candidate and the minimum time, and attaches the new sample to that candidate's ancestral lineage at that time. After all samples are threaded, a postprocessing step called ARG normalization refines the node times by a monotonically increasing map matched to node-time quantiles under the demographic prior; it preserves the time ordering of nodes and so does not alter the topology (Methods). The output is a single estimated graph. The source refers to the Methods and its Supplementary Note 1 for theoretical guarantees and properties of the algorithm, and evaluates the accuracy of the reconstruction on simulated data; this page states no accuracy guarantee.

## Expansion

1. The threading instruction: at each position a chosen sample and a joining time, from the hashing shortlist and the ASMC estimates.
2. The threading operation and the validity of the graph after each insertion (every marginal tree remains a tree on the threaded samples, with parents older than children).
3. The ARG normalization step and its definition.
4. Statistics computed from the resulting graph, such as genealogy-based association tests, as separate statements.

## Sources

- B. C. Zhang, A. Biddanda, Á. F. Gunnarsson, F. Cooper and P. F. Palamara, Biobank-scale inference of ancestral recombination graphs enables genealogical analysis of complex traits, Nat. Genet. 55 (2023), 768–776, Results (overview of ARG-Needle, Fig. 1) and Methods. <https://doi.org/10.1038/s41588-023-01379-x>
