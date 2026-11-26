# Mark Step

Serve a request. A hit marks the page. A miss with room loads and marks the page. A miss
with zero capacity caches nothing. A miss on a full cache starts a new phase if every cached page
is marked, evicts `victim R s`, then loads and marks the page.
