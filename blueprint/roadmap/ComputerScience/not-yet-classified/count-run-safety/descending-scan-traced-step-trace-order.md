# Descending Scan Traced step trace order

One active descending step has the same two-read instrumentation order;
after those reads the `next < previous` arm is selected before the reverse
comparison can control the branch.
