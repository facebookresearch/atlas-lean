# CDCLStep

CDCL steps without restart or clause deletion: decide a
literal whose variable is not yet decided (neither polarity
present), or learn a new clause implied by `F` and backjump to a
suffix of the trail.
