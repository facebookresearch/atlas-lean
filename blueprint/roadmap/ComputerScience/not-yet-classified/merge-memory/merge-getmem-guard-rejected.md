# Merge Getmem guard Rejected

An oversized request observes the post-`merge_freemem` state because the C
source frees old heap storage before checking the unsigned allocation bound.
