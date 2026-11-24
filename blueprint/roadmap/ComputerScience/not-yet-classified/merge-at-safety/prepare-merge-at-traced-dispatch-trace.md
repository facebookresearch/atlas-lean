# Prepare Merge At Traced dispatch trace

Every successful non-early preparation trace contains the two trimming
gallops in source order: the right gallop, the last-A endpoint read selected by
its result, and then the left gallop.  The equality also fixes all preceding
pending-stack and first-B observations.
