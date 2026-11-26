# Min-hash read mapping

Read mapping by locality-sensitive hashing: reference windows and reads are summarized by min-hash signatures of their $q$-gram sets, so that a read collides with the windows whose $q$-gram content is most similar in Jaccard terms, which tolerates high sequencing error rates and known variants inserted into the index.

- [Min-hash signature agreement is binomial in the Jaccard coefficient](min-hash-signature-agreement-is-binomial-in-the-jaccard-coefficient.md)
