# Erase Bucket With Cost cost le

Erasing a key from a single bucket by the counted scan (one event per entry compared until the first entry with that key, counting that comparison, or one terminal event when there is none) takes at most $1 + n$ scan events, where $n$ is the length of the bucket.
