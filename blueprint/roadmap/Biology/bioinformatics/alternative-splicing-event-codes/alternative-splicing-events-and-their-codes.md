# Alternative splicing events and their codes

**Sites.** A *site* $s$ is an exon boundary of an annotated transcript, with genomic position $\mathrm{pos}(s)$ and type $\mathrm{type}(s) \in \{\sigma, \delta, \alpha, \omega\}$ (transcription start, splice donor, splice acceptor, polyadenylation). A transcript is the sequence of its sites ordered by position; a virtual first and last site is added to every transcript of a locus.

**Definitions.** Compare two transcripts $S_t, S_u$ of a locus.

1. A site is *variable* if exactly one of $S_t, S_u$ uses it, and *common* if both do.
2. A variable site is an *alternative splice site* if it is a donor or acceptor and lies within the genomic region covered by both primary transcripts.
3. An *AS event* is a maximal run $s_1 < \dots < s_g$ (in genomic order) of variable sites lying strictly between two consecutive common sites $s_0$ and $s_{g+1}$, such that the sites of each transcript inside the run are consecutive in that transcript, and at least one $s_i$ is an alternative splice site.

**AS code.** Number the variable sites of an event $1, \dots, g$ from 5' to 3' and attach to each a symbol from $\{[\,,\ \hat{}\ ,\ -\,,\ ]\}$ for start, donor, acceptor and polyadenylation sites. Each transcript's structure inside the event is the concatenation of its numbered symbols, or $0$ if it uses no variable site; the code is the comma-separated list of the two structures ordered by their first site. Examples:

| event | code |
|---|---|
| exon skipping | `0,1-2^` |
| intron retention | `0,1^2-` |
| alternative donor | `1^,2^` |
| alternative acceptor | `1-,2-` |
| mutually exclusive exons | `1-2^,3-4^` |

**Proposition.** The code is a complete invariant of the relative exon–intron structure of an event: two events have the same code exactly when their variable sites, listed in genomic order, have the same types and the same assignment to the two transcripts. In particular every pairwise variation, including ones not covered by the classical categories, receives a code.

## Expansion

Within an event, positions matter only through their order, and each variable site belongs to exactly one transcript. The code records for every rank $i$ its type and which transcript uses it, and conversely the type sequence and the transcript assignment can be read back from the code, which proves the proposition. Common flanks delimit events so that variations across adjacent introns linked by exon definition, and variations of transcript ends that co-occur with splicing, are kept in one event rather than split. The source reports codes such as `1^3-,2^4-` for overlapping donor and acceptor variation and shows that a few codes account for most events while many rare structures occur in reference annotations.

## Sources

- M. Sammeth, S. Foissac and R. Guigó, *A general definition and nomenclature for alternative splicing events*, PLoS Computational Biology (2008). <https://doi.org/10.1371/journal.pcbi.1000147> (PMCID: PMC2467475). Results: Definitions 1–4 and "A Flexible Code for Alternative Splicing Events".
